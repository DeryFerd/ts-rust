#!/bin/bash
# usage: bound2.sh <round>. Bound parity run for the checker-port candidate: copies the release goport,
# goport_emit and goport_typesyms, records commit/fingerprint/binary/oracle hashes, then runs the
# type-check measures (core, extra, sweep, sweep-extra2) and the emit project comparison.
set -u
cd /home/theo/Code/sandbox/ts-rust
R=$1; O=target/continuation-r97-goport/measure/$R; mkdir -p $O
WT=target/worktrees/checker-port
REL=${GOPORT_REL:-target/continuation-r97-goport/runtime/cargo-target/release}
test -z "$(git -C $WT status --porcelain crates/ts_goport Cargo.toml Cargo.lock crates/ts_compiler/src/lib.rs)" || { echo "dirty allowed files"; exit 1; }
for b in goport goport_emit goport_typesyms; do cp $REL/$b $O/$b.bin; done
export GOPORT_BIN=$PWD/$O/goport.bin
bash /home/theo/Code/sandbox/ts-rust/scripts/goport/measure.sh $R > $O/summary-main.txt 2>&1
bash /home/theo/Code/sandbox/ts-rust/scripts/goport/measure-extra.sh $R > $O/summary-extra.txt 2>&1
bash /home/theo/Code/sandbox/ts-rust/scripts/goport/sweep.sh $R > $O/summary-sweep.txt 2>&1
bash target/project-inputs-extra/sweep-extra2.sh $R > $O/summary-sweep-extra2.txt 2>&1
bash target/continuation-r97-goport/emit/compare-emit.sh $PWD/$O/goport_emit.bin $R > $O/summary-emit.txt 2>&1
python3 - "$O" "$WT" <<'PY'
import sys,json,hashlib,subprocess,datetime,os
o,wt=sys.argv[1],sys.argv[2]
h=lambda p: hashlib.sha256(open(p,'rb').read()).hexdigest()
fp=subprocess.check_output(['python3','/home/theo/Code/sandbox/ts-rust/scripts/goport/fp.py',wt],text=True).split()
m={"commit":subprocess.check_output(['git','-C',wt,'rev-parse','HEAD'],text=True).strip(),"sourceFingerprint":fp[0],
 "binaries":{b:h(f'{o}/{b}.bin') for b in ['goport','goport_emit','goport_typesyms']},
 "oracle":os.path.expanduser('~/.local/bin/tsgo-oracle'),"oracleSha256":h(os.path.expanduser('~/.local/bin/tsgo-oracle')),
 "completedUtc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "summaries":{f:open(o+'/'+f).read().splitlines()[-60:] for f in sorted(os.listdir(o)) if f.startswith('summary-')},
 "outputs":{f:h(o+'/'+f) for f in sorted(os.listdir(o)) if f.endswith(('.out','.err'))}}
json.dump(m,open(o+'/manifest.json','w'),indent=1)
print(m['commit'][:9],m['sourceFingerprint'][:12],{k:v[:12] for k,v in m['binaries'].items()})
PY
