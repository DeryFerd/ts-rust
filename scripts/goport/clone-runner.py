# usage: clone-runner.py <from> <to> <batch-id>. Copies continuation-r<from> runner scripts to r<to>,
# keeps the warm cargo target, updates the batch id and the preparation manifest hash constant.
import sys,shutil,hashlib,re
from pathlib import Path
a,b,bid=sys.argv[1:4]
t=Path('/home/theo/Code/sandbox/ts-rust/target')
A,B=f'continuation-r{a}',f'continuation-r{b}'
def sub(s):
    s=s.replace('continuation-r104-cargo-target','@@T@@').replace(A,B).replace('@@T@@','continuation-r104-cargo-target')
    s=s.replace(f"'r{a}-",f"'r{b}-").replace(f'R{a}',f'R{b}')
    s=s.replace('recovery-continuation-go-checker-port-1',bid).replace(re.sub(r'-\d+$','',bid)+'-'+str(int(bid.rsplit('-',1)[1])-1),bid)
    return s
for p in t.glob(A+'-*'):
    if p.is_file() and p.suffix in ('.sh','.py','.cjs') and 'drive' not in p.name and 'check-result' not in p.name:
        q=t/p.name.replace(A,B); assert not q.exists(); q.write_text(sub(p.read_text())); q.chmod(p.stat().st_mode)
for d in ('runtime-env','current-source-corpus'):
    src,dst=t/f'{A}-{d}',t/f'{B}-{d}'; dst.mkdir()
    for p in src.iterdir():
        if p.is_dir():
            if p.name=='cargo-home': shutil.copytree(p,dst/p.name)
            continue
        if p.name.endswith('-config.toml') or p.name.startswith('prebuild-config'): continue
        if d=='runtime-env' and p.suffix in ('.py','.cjs','.toml','.json'):
            s=sub(p.read_text())
            if p.name=='preparation-manifest.json': s=re.sub(r'"plannedRevision": \d+',f'"plannedRevision": {b}',s)
            (dst/p.name).write_text(s)
        elif d=='current-source-corpus' and p.suffix in ('.py','.sh','.cjs') and p.name!='bound-comparator.cjs':
            (dst/p.name).write_text(sub(p.read_text())); (dst/p.name).chmod(p.stat().st_mode)
old=hashlib.sha256((t/f'{A}-runtime-env/preparation-manifest.json').read_bytes()).hexdigest()
new=hashlib.sha256((t/f'{B}-runtime-env/preparation-manifest.json').read_bytes()).hexdigest()
for p in list(t.glob(B+'-*'))+list((t/f'{B}-runtime-env').iterdir())+list((t/f'{B}-current-source-corpus').iterdir()):
    if p.is_file() and p.suffix in ('.py','.cjs','.sh'):
        s=p.read_text()
        if old in s: p.write_text(s.replace(old,new))
print(new)
