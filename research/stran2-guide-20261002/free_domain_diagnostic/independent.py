"""Independent ordinary binary-AIGER evaluation; no search/formal imports."""
import io
from pathlib import Path

class Aig:
    def __init__(self, path):
        f=io.BytesIO(Path(path).read_bytes()); h=f.readline().split()
        assert h[0]==b'aig' and len(h)>=6
        self.m,self.ni,self.nl,self.no,self.na=map(int,h[1:6])
        assert not any(map(int,h[6:])) and self.m==self.ni+self.nl+self.na
        self.latches=[]
        for _ in range(self.nl):
            row=list(map(int,f.readline().split()))
            assert len(row) in (1,2) and (len(row)==1 or row[1]==0)
            self.latches.append(row[0])
        self.outputs=[int(f.readline()) for _ in range(self.no)]
        def varint():
            value=shift=0
            while True:
                b=f.read(1); assert b
                b=b[0]; value |= (b&127)<<shift
                if b<128: return value
                shift+=7
        self.gates=[]
        for node in range(self.ni+self.nl+1,self.m+1):
            hi=2*node-varint();lo=hi-varint()
            assert 0<=lo<=hi<2*node
            self.gates.append((hi,lo))
    def values(self, inputs, state):
        assert len(inputs)==self.ni and len(state)==self.nl
        assert all(type(x) is int and x in (0,1) for x in inputs+state)
        values=[0]+inputs+state
        for x,y in self.gates:
            values.append((values[x//2]^(x&1))&(values[y//2]^(y&1)))
        assert len(values)==self.m+1
        return values
    def successor(self, values):
        return [values[x//2]^(x&1) for x in self.latches]

def recipe(recipe, out, values):
    built=[]
    def val(code):
        if code>=0: return values[code//2]^(code&1)
        assert code<=-2
        n,p=divmod(-code-2,2); assert n<len(built)
        return built[n]^p
    assert len(recipe)%2==0
    for i in range(0,len(recipe),2): built.append(val(recipe[i])&val(recipe[i+1]))
    return val(out)

def witness(a, c, saved, free=None):
    values=a.values(saved['inputs'],saved['state'])
    old=values[c['root']];new=recipe(c['recipe'],c['out'],values)
    assert old!=new and (old,new)==(saved['root'],saved['replacement'])
    if free is not None:
        lane=saved['lane']
        assert values==[(sig>>lane)&1 for sig in free]
    return True
