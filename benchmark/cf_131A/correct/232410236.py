#CF_Problem:	131A_Caps_Lock

def capsLock(s):
	if len(s) == 1 or s[1:].isupper():
		return s.swapcase()
	return s


s = input()
print(capsLock(s))