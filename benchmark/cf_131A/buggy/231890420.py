n = input()
print("Caps") if n in [n.lower(), n[0]+n[1:].upper()] else print("Lock")