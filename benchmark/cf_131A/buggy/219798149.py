def main():
    s = input();
    if s.isupper():
        return s.lower()
    if s[1:].isupper():
        return s.capitalize()
    return s
print(main())