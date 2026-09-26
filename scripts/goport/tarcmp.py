import tarfile,hashlib,os,sys
tar,root=sys.argv[1],sys.argv[2]
t=tarfile.open(tar)
names=set();bad=[]
for m in t.getmembers():
    n=m.name[2:] if m.name.startswith('./') else m.name
    if not n: continue
    rel=n.split('/',1)[1] if n.split('/',1)[0]=='source' and '/' in n else n
    if m.isfile():
        names.add(rel)
        p=os.path.join(root,rel)
        if not os.path.isfile(p): bad.append(('missing',rel));continue
        if hashlib.sha256(t.extractfile(m).read()).digest()!=hashlib.sha256(open(p,'rb').read()).digest(): bad.append(('diff',rel))
extra=[]
for d,ds,fs in os.walk(root):
    for f in fs:
        rel=os.path.relpath(os.path.join(d,f),root)
        if rel not in names and not rel.startswith('node_modules/'): extra.append(rel)
print('tarfiles',len(names),'bad',bad[:10],len(bad),'extra',extra[:10],len(extra))
