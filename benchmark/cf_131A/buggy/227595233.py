counter_capital=0
counter_small=0
word=input()
lol=len(word)
for i in word:
    if i==i.capitalize():
        counter_capital+=1
    else:
        counter_small+=1    
if lol==1:
    print(word.capitalize())
if (lol!=1) and ((counter_capital)>(counter_small)):
    print(word[0].capitalize()+word[1::].lower()) 
if (lol!=1) and ((counter_capital)<(counter_small)):
    print(word)