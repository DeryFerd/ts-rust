#!/bin/bash
# usage: bound.sh <round>. Copies the release goport, records commit/binary/oracle hashes, runs all measures, saves summaries with exit codes.
set -u
cd /home/theo/Code/sandbox/ts-rust
R=$1; O=target/continuation-r97-goport/measure/$R; mkdir -p $O
WT=target/worktrees/checker-port
cp target/continuation-r97-goport/runtime/cargo-target/release/goport $O/goport.bin
test -z "$(git -C $WT status --porcelain | grep -v '^?? crates/ts_goport/CANDIDATE.md$')" || { echo "dirty checkout"; exit 1; }
export GOPORT_BIN=$PWD/$O/goport.bin
bash /home/theo/Code/sandbox/ts-rust/scripts/goport/measure.sh $R > $O/summary-main.txt 2>&1
bash /home/theo/Code/sandbox/ts-rust/scripts/goport/measure-extra.sh $R > $O/summary-extra.txt 2>&1
bash /home/theo/Code/sandbox/ts-rust/scripts/goport/sweep.sh $R > $O/summary-sweep.txt 2>&1
python3 - "$O" "$WT" <<'PY'
import sys,json,hashlib,subprocess,datetime,os
o,wt=sys.argv[1],sys.argv[2]
h=lambda p: hashlib.sha256(open(p,'rb').read()).hexdigest()
m={"commit":subprocess.check_output(['git','-C',wt,'rev-parse','HEAD'],text=True).strip(),
 "goportSha256":h(o+'/goport.bin'),"oracle":os.path.expanduser('~/.local/bin/tsgo-oracle'),
 "oracleSha256":h(os.path.expanduser('~/.local/bin/tsgo-oracle')),
 "oracleCommand":"tsgo-oracle -p <tsconfig> --noEmit --pretty false --tsBuildInfoFile <path outside inputs>",
 "completedUtc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "summaries":{f:open(o+'/'+f).read().splitlines() for f in ['summary-main.txt','summary-extra.txt','summary-sweep.txt']},
 "outputs":{f:h(o+'/'+f) for f in sorted(os.listdir(o)) if f.endswith(('.out','.err'))}}
json.dump(m,open(o+'/manifest.json','w'),indent=1)
print(json.dumps(m['summaries'],indent=1))
PY
