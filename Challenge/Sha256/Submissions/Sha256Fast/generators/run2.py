import hashlib, random, sys
from evm import execute
from vectors import VECTORS, REFERENCE_GAS
import importlib
mod = importlib.import_module(sys.argv[1] if len(sys.argv)>1 else "sha256gen2")
code = mod.generate()
print(f"size {len(code)} bytes")
tot=tref=0; allok=True
for (label,data),ref in zip(VECTORS, REFERENCE_GAS):
    h,gas,vm = execute(code, data)
    ok = h.kind=="return" and h.data==hashlib.sha256(data).digest()
    allok &= ok; tot+=gas; tref+=ref
    print(f"{label:26s} {'ok ' if ok else 'BAD'} gas={gas:9d} ref={ref:9d} {ref/gas:6.2f}x")
print(f"{'TOTAL':26s}     gas={tot:9d} ref={tref:9d} {tref/tot:6.2f}x")
random.seed(11); bad=0
for n in list(range(0,260))+[511,512,513,1000,1024,2000,4096]:
    d = bytes(random.randrange(256) for _ in range(n))
    h,gas,vm = execute(code, d)
    if h.kind!="return" or h.data!=hashlib.sha256(d).digest():
        bad+=1
        if bad<5: print("FAIL n=",n,h.kind)
print(("fuzz clean" if bad==0 else f"fuzz {bad} FAILURES"), "|", "vectors correct" if allok else "*** VECTORS INCORRECT ***")
