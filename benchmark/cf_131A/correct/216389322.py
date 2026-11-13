s = input()
caps_lock  = True
for i in range(1,len(s)):
    if s[i] >= 'a' and s[i] <= 'z':
        caps_lock = False
        break
if caps_lock:
    print(s.swapcase())
else:
    print(s)