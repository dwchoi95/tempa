def es_numero_de_la_suerte(n):
    d = [int(x) for x in str(n)]
    return all(digit == 4 or digit == 7 for digit in d)

def contar_digitos_de_la_suerte(n):
    d = [int(x) for x in str(n)]
    return sum(1 for digit in d if digit == 4 or digit == 7)

def main():
    n = int(input())
    
    num_digitos_suerte = contar_digitos_de_la_suerte(n)

    if es_numero_de_la_suerte(num_digitos_suerte):
        print("YES")
    else:
        print("NO")

if __name__ == "__main__":
    main()