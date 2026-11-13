def toggle_case(s):
    if not s.isalpha():
        return s
    return s.lower() if s.isupper() else s.upper()

def apply_rule(word):
    if word.isupper() or word[1:].isupper():
        return ''.join(toggle_case(c) for c in word)
    return word

print(apply_rule("hELLO")) # hello
print(apply_rule("HTTP"))   # http
print(apply_rule("z"))      # Z
print(apply_rule("Hello")) # Hello