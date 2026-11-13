s = input()

if s.isupper():
    corrected_word = s.lower()
elif s[0].islower() and s[1:].isupper():
    corrected_word = s[0].upper() + s[1:].lower()
elif len(s) == 1:
    corrected_word = s.upper()
else:
    corrected_word = s

print(corrected_word)