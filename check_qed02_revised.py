import sys
sys.path.insert(0, '.')
from parser import parse_equation
_, v = parse_equation('(Q3/Vc)+(Q4/Vc)=0')
assert v == ['Q3', 'Q4', 'Vc'], v
_, v = parse_equation('(-ka_rate)+(ka_rate)=0')
assert v == ['ka_rate'], v
_, v = parse_equation('Q10+Q1=0')
assert 'Q10' in v and 'Q1' in v and 'Q' not in v, v
n, _ = parse_equation('a ' + chr(92) + 'cdotp b=c')
assert n is None, 'cdotp must fail closed'
print('qed-02 revised asserts OK')
