def get_input(pregunta=""):
    return list(map(int, input(pregunta).split(" ")))

line_1 = get_input()
line_2 = get_input()

#objs = line_2[:line_1[0]]
dias = 0
fin = False
objs = line_2[:line_1[0]]


while not fin:
    temp_stack = line_2.copy()
    temp = objs.copy()
    for j in objs:
        if j in temp_stack:
            temp.remove(j)
            line_2.remove(j)
    if len(temp) > 0:
        fin = True
    else:
        dias = dias + 1 

print(dias)