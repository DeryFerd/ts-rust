import os,hashlib,sys
root=sys.argv[1];h=hashlib.sha256();n=0
for d,ds,fs in sorted(os.walk(root)):
    ds.sort()
    if os.path.relpath(d,root).split(os.sep)[0] in ('node_modules','.git'): continue
    for f in sorted(fs):
        p=os.path.join(d,f);rel=os.path.relpath(p,root)
        if os.path.islink(p): continue
        h.update(rel.encode()+b'\0'+open(p,'rb').read()+b'\0');n+=1
print(h.hexdigest(),n)
