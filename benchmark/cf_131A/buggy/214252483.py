s = input()

result = s.lower() if s.isupper() else s[0].upper() + s[1:].lower() \
                    if s[0].islower() and len(s) >= 2 else s
print(result)