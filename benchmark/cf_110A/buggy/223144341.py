def nearlyLucky(fortuna):
    count = 0

    while fortuna>0:
        if fortuna % 10 == 4 or fortuna % 10 == 7:
            count +=1
            fortuna //= 10

            return count ==4 or count == 7     
if __name__ == "__main__":
    fortuna = int(input())
    print ("si" if nearlyLucky(fortuna) else "no")