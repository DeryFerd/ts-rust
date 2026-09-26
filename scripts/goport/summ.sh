#!/bin/bash
# summ.sh <out> <err>: cluster diagnostics by code and panics by site
echo "diag codes:"; grep -oE "error TS[0-9]+" $1 | sort | uniq -c | sort -nr | head -15
echo "files with diags:"; grep -oE "^[^(]+" $1 | sed 's|.*/||' | sort | uniq -c | sort -nr | head -8
echo "panics:"; grep "^goport: panic" $2 | sed 's/: [^:]*$//' | sort | uniq -c | sort -nr | head -20
echo "unported:"; grep '^unported' $2 | sort -k3 -nr | head -20
