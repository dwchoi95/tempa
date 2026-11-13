n = input("")
def Check(par):
  for d in par :
    if d != "4" and d != "7":
      return "NO"
  return "YES"
print(Check(n))