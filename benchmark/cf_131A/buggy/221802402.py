def main():
    # input
    s = input()

    # soln
    if s == s.upper() or s[1:] == s[1:].upper():
        s = s.title()
    print(s)

if __name__ == "__main__":
    main()