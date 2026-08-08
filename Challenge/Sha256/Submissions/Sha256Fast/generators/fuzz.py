import hashlib, random
from evm import execute
import sha256gen
code = sha256gen.generate()
random.seed(7)
bad = 0
lens = list(range(0, 200)) + [255,256,257,511,512,513,1000,1023,1024,1025,2000,4096]
for n in lens:
    data = bytes(random.randrange(256) for _ in range(n))
    h, gas, vm = execute(code, data)
    if h.kind != "return" or h.data != hashlib.sha256(data).digest():
        print("FAIL", n, h.kind); bad += 1
print(f"{len(lens)} lengths tested, {bad} failures")
