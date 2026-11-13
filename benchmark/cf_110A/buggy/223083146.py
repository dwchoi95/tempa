angka = input()
jumlah=0
for karakter in angka:
    if karakter.isdigit():
        jumlah += 1
if jumlah == 4 or jumlah == 7:
    print("YES")
else:
    print("NO")