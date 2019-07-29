// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gc

import (
	"cmd/compile/internal/types"
	"cmd/internal/obj"
	"strings"
)

// A function named init is a special case.
// It is called by the initialization before main is run.
// To make it unique within a package and also uncallable,
// the name, normally "pkg.init", is altered to "pkg.init.0".
var renameinitgen int

// Dummy function for autotmps generated during typechecking.
var dummyInitFn = nod(ODCLFUNC, nil, nil)

func renameinit() *types.Sym {
	s := lookupN("init.", renameinitgen)
	renameinitgen++
	return s
}

func buildinitfunc(name string, body []*Node) *types.Sym {
	lineno = body[0].Pos
	initvarfn := lookup(name)
	disableExport(initvarfn)
	fn := dclfunc(initvarfn, nod(OTFUNC, nil, nil))
	for _, dcl := range dummyInitFn.Func.Dcl {
		dcl.Name.Curfn = fn
	}
	fn.Func.Dcl = append(fn.Func.Dcl, dummyInitFn.Func.Dcl...)
	dummyInitFn.Func.Dcl = nil

	fn.Nbody.Set(body)
	funcbody()

	fn = typecheck(fn, ctxStmt)
	Curfn = fn
	typecheckslice(body, ctxStmt)
	Curfn = nil
	funccompile(fn)
	return initvarfn
}

// fninit makes an initialization record for the package.
// See runtime/proc.go:initTask for its layout.
// The 3 tasks for initialization are:
//   1) Initialize all of the packages the current package depends on.
//   2) Initialize all the variables that have initializers.
//   3) Run any user-defined init functions.
func fninit(n []*Node) {

	// Find all the statements that initialize global variables and need to
	// be executed at startup; we will be creating init functions for each of
	// these.
	nf := initOrder(n)

	var deps []*obj.LSym   // initTask records for packages the current package depends on
	var fns []*obj.LSym    // functions to call for package initialization
	var varfns []*obj.LSym // functions to call to initialize variables (generated)

	// Find imported packages with init tasks.
	for _, s := range types.InitSyms {
		deps = append(deps, s.Linksym())
	}

	var initvarNotPure []*Node

	// For each statement that initializes a global variable, create a init function
	// called init.var.NN. We create separate functions (rather than a single one)
	// because the linker might be able to remove them, if the corresponding
	// variable ends up being unused.
	for i := 0; i < len(nf); i++ {
		var body []*Node

		// Record that the initialized variable(s) (LHS of the assign statement)
		// have an initialization function associated to them. This will allow
		// ggloblnod() later to emit relocations for them.
		var varname string
		switch nf[i].Op {
		case OAS:
			varname = nf[i].Left.Sym.Name

			// Slice literals might have the backing array allocated statically,
			// and assignments are generated to temporary slots (before going
			// into the backing store). Treat these as non-pure: we do not
			// have a good way of handling them as we don't know which
			// variable they refer to.
			if strings.HasPrefix(varname, ".stmp_") {
				initvarNotPure = append(initvarNotPure, nf[i])
				continue
			}
			nf[i].Left.SetHasInitFunc(true)

			// Struct literals might generate init functions, in case of large
			// structures where only some fields are initialized. In this case,
			// we need to generate a single symbol for all the assignments that
			// refer to the same variable.
			var j int
			for j = i + 1; j < len(nf); j++ {
				if !(nf[j].Op == OAS && nf[j].Left.Sym.Name == nf[i].Left.Sym.Name) {
					break
				}
			}
			body = nf[i:j]
			i = j - 1
		case OAS2FUNC, OAS2DOTTYPE, OAS2MAPR, OAS2RECV:
			nf[i].List.First().SetHasInitFunc(true)
			//FIXME: must refer to same init function, or create wrapper
			//nf[i].List.Second().SetHasInitFunc(true)
			varname = nf[i].List.First().Sym.Name
			body = nf[i : i+1]
		default:
			Fatalf("unknown init statement: %v", n)
		}

		initvarfn := buildinitfunc("init.var."+varname, body)
		varfns = append(varfns, initvarfn.Linksym())
	}

	if len(initvarNotPure) != 0 {
		initotherfn := buildinitfunc("init.other", initvarNotPure)
		fns = append(fns, initotherfn.Linksym())
	}

	if dummyInitFn.Func.Dcl != nil {
		// We only generate temps using dummyInitFn if there
		// are package-scope initialization statements, so
		// something's weird if we get here.
		Fatalf("dummyInitFn still has declarations")
	}

	// Record user init functions.
	for i := 0; i < renameinitgen; i++ {
		s := lookupN("init.", i)
		fns = append(fns, s.Linksym())
	}

	if len(deps) == 0 && len(fns) == 0 && len(varfns) == 0 && localpkg.Name != "main" && localpkg.Name != "runtime" {
		return // nothing to initialize
	}

	// Make an .inittask structure, that will be processed by the runtime
	sym := lookup(".inittask")
	nn := newname(sym)
	nn.Type = types.Types[TUINT8] // dummy type
	nn.SetClass(PEXTERN)
	sym.Def = asTypesNode(nn)
	exportsym(nn)
	lsym := sym.Linksym()
	ot := 0
	ot = duintptr(lsym, ot, 0) // state: not initialized yet
	ot = duintptr(lsym, ot, uint64(len(deps)))
	ot = duintptr(lsym, ot, uint64(len(fns)))
	ot = duintptr(lsym, ot, uint64(len(varfns)))
	for _, d := range deps {
		ot = dsymptr(lsym, ot, d, 0)
	}
	for _, f := range fns {
		ot = dsymptr(lsym, ot, f, 0)
	}
	for _, f := range varfns {
		ot = dsymptr(lsym, ot, f, 0)
	}
	// An initTask has pointers, but none into the Go heap.
	// It's not quite read only, the state field must be modifiable.
	ggloblsym(lsym, int32(ot), obj.NOPTR)

	/*
		// For each init.var function, save the corresponding variable name into
		// a table. This will be used by the linker to remove init.var functions
		// that initialise unused functions. Rather than storing these names within
		// .inittask, we use a different symbol so that this table itself will
		// be removed by the final binary (as it's only useful to the linker).
		sym = lookup(".initvarnames")
		nn = newname(sym)
		nn.Type = types.Types[TUINT8] // dummy type
		nn.SetClass(PEXTERN)
		sym.Def = asTypesNode(nn)
		exportsym(nn)
		lsym = sym.Linksym()
		ot = 0
		ot = duintptr(lsym, ot, uint64(len(nf)))
		for _, f := range nf {
			switch f.Op {
			case OAS:
				ot = duint8(lsym, ot, 0xcd) // 1 => single variable reference
				ot = dsymptr(lsym, ot, f.Left.Sym.Linksym(), 0)
			case OAS2FUNC, OAS2DOTTYPE, OAS2MAPR, OAS2RECV:
				ot = duint8(lsym, ot, 0xcc) // 2 => double variable reference
				ot = dsymptr(lsym, ot, f.List.First().Sym.Linksym(), 0)
				ot = dsymptr(lsym, ot, f.List.Second().Sym.Linksym(), 0)
			default:
				Fatalf("unknown init statement: %v", n)
			}
		}
		// FIXME(rasky): check if obj.NOPTR is required. Probably flags don't
		// matter as this symbol is going away during linking.
		ggloblsym(lsym, int32(ot), obj.NOPTR)
	*/
}

func (n *Node) checkInitFuncSignature() {
	if n.Type.NumRecvs()+n.Type.NumParams()+n.Type.NumResults() > 0 {
		Fatalf("init function cannot have receiver, params, or results: %v (%v)", n, n.Type)
	}
}
