#!/bin/bash
# Builds and runs an XelSSL test program: build_test.sh t_prim

set -e
T=${1:-t_prim}
cd "$(dirname "$0")/../.."
mkdir -p xelssl/test/out
export MSYS2_ARG_CONV_EXCL='*'
"C:/lazarus64/fpc/3.2.2/bin/x86_64-win64/fpc.exe" -O2 -Mobjfpc -Sh -vewn \
  -FExelssl/test/out -FUxelssl/test/out -Fuxelssl "xelssl/test/$T.pas" \
  | grep -vE "^(Hint|Note)" | grep -E "Error|Fatal|Warning: .*xelssl|lines compiled" || true
shift || true
"xelssl/test/out/$T.exe" "$@"
