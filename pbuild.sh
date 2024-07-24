#!/bin/bash

if ! [ -f .lake/packages/aesop/.lake/build/lib/libAesop.dylib ]; then
    lake build Aesop:shared
fi

if ! [ -f .lake/packages/Cli/.lake/build/lib/libCli.dylib ]; then
    lake build Cli:shared
fi

if ! [ -f .lake/packages/importGraph/.lake/build/lib/libImportGraph.dylib ]; then
    lake build ImportGraph:shared
fi

if ! [ -f .lake/packages/mathlib/.lake/build/lib/libMathlib.dylib ]; then
    lake build Mathlib:shared
fi

if ! [ -f .lake/packages/proofwidgets/.lake/build/lib/libProofWidgets.dylib ]; then
    lake build ProofWidgets:shared
fi

if ! [ -f .lake/packages/Qq/.lake/build/lib/libQq.dylib ]; then
    lake build Qq:shared
fi

if ! [ -f .lake/packages/batteries/.lake/build/lib/libBatteries.dylib ]; then
    lake build Batteries:shared
fi

lake build SampCert:shared
