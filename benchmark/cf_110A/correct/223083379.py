angka = input()
jumlah=0
for karakter in angka:
    if karakter== '4' or karakter =='7':
        jumlah += 1
if jumlah == 4 or jumlah == 7:
    print("YES")
else:
    print("NO")