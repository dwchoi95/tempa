if __name__ == "__main__":
    num = input()
    luckyDigits = int(num.count('4')) + int(num.count('7'))

    if(luckyDigits == 4 or luckyDigits == 7):
        print("YES")
    else:
        print("NO")