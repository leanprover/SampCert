#!/bin/bash

lake build Aesop:shared
lake build Cli:shared
lake build ImportGraph:shared
if ! [ -f .lake/packages/mathlib/.lake/build/lib/libMathlib.dylib ]; then
    lake build Mathlib:shared
fi
lake build ProofWidgets:shared
lake build Qq:shared
lake build Batteries:shared
lake build SampCert:shared
