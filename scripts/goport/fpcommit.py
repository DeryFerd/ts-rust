# Fingerprint (same method as fp.py) of the worktree as it was at <commit>: files in the scope of a
# goport revision (every path except the saved state under docs/ and target/) come from the commit;
# the saved state and untracked files (such as the CANDIDATE.md marker) come from the current tree.
# usage: fpcommit.py <checkout> <commit>   prints "<sha256> <file count>", like fp.py
import hashlib,subprocess,sys,os
root,commit=sys.argv[1],sys.argv[2]
excluded=(b'docs/typechecker-state/',b'docs/typechecker-batches/',b'target/')
g=lambda *a: subprocess.run(['git','-C',root,*a],capture_output=True,check=True).stdout
cur=[f for f in g('ls-files','--cached','-z').split(b'\0') if f and f.startswith(excluded)]
cur+=[f for f in g('ls-files','--others','--exclude-standard','-z').split(b'\0') if f]
com=[f for f in g('ls-tree','-r','--name-only','-z',commit).split(b'\0') if f and not f.startswith(excluded)]
com_set=set(com)
h=hashlib.sha256();n=0
for f in sorted(set(cur)|set(com)):
    if f in com_set: data=g('show',commit+':'+f.decode())
    else:
        p=os.path.join(root.encode(),f)
        if not os.path.isfile(p): continue
        data=open(p,'rb').read()
    h.update(f+b'\0'+data+b'\0'); n+=1
print(h.hexdigest(),n)
