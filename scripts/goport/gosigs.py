import re,sys,collections,glob
files=[f for f in sorted(glob.glob('*.go')) if not f.endswith('_test.go')]
sig=re.compile(r'^func (\((\w+) \*?(\w+)\) )?(\w+)(\[[^\]]*\])?\((.*)\)\s*(.*?)\s*\{\s*$')
ptypes=collections.Counter(); rtypes=collections.Counter(); n=0; bad=[]
def split_params(s):
    out=[];depth=0;cur=''
    for ch in s:
        if ch in '([{':depth+=1
        if ch in ')]}':depth-=1
        if ch==',' and depth==0: out.append(cur.strip());cur=''
        else: cur+=ch
    if cur.strip(): out.append(cur.strip())
    return out
for f in files:
    for i,l in enumerate(open(f)):
        if not l.startswith('func '): continue
        m=sig.match(l.rstrip())
        if not m: bad.append((f,i+1,l.strip()[:120])); continue
        n+=1
        ps=split_params(m.group(6))
        # go allows "a, b *Type"
        types=[]
        for p in ps:
            parts=p.split(' ',1)
            types.append(parts[1] if len(parts)==2 else None)
        for t in types:
            if t: ptypes[t]+=1
        r=m.group(7)
        if r.startswith('('): 
            for p in split_params(r[1:-1]):
                parts=p.split(' ',1); rtypes[parts[-1]]+=1
        elif r: rtypes[r]+=1
print('parsed',n,'bad',len(bad))
for b in bad[:15]: print('BAD',b)
print('PARAM types',len(ptypes))
for t,c in ptypes.most_common(): print(c,t)
print('RET types',len(rtypes))
for t,c in rtypes.most_common(): print(c,t)
