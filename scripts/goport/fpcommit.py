# Fingerprint (same method as fp.py) of the worktree as it was at <commit>:
# files under the R97 allowed paths come from the commit, all other files from the current tree.
import hashlib,subprocess,sys,os
root,commit=sys.argv[1],sys.argv[2]
allowed=(b'crates/ts_goport/',b'Cargo.toml',b'Cargo.lock',b'crates/ts_compiler/src/lib.rs')
g=lambda *a: subprocess.run(['git','-C',root,*a],capture_output=True,check=True).stdout
cur=[f for f in g('ls-files','--cached','--others','--exclude-standard','-z').split(b'\0') if f and not f.startswith(allowed)]
com=[f for f in g('ls-tree','-r','--name-only','-z',commit).split(b'\0') if f and f.startswith(allowed)]
h=hashlib.sha256();n=0
for f in sorted(set(cur)|set(com)):
    if f.startswith(allowed): data=g('show',commit.encode().decode()+':'+f.decode())
    else:
        p=os.path.join(root.encode(),f)
        if not os.path.isfile(p): continue
        data=open(p,'rb').read()
    h.update(f+b'\0'+data+b'\0'); n+=1
print(h.hexdigest(),n)
