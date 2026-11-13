from itertools import *
from functools import *

print((lambda x,
       la = (lambda y: y[1:].isupper()),
       inverse = (lambda y:
                  ''.join(map((lambda x:
                           x.lower() if x.isupper() else x.upper()),
                          y)))
       :
       inverse(x) if la(x) else x)(input()))