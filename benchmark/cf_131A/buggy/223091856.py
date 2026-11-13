sequence=input()
first=sequence[0]
sequence_edit=sequence[1:]
if(sequence_edit.isupper()):
    print(first.upper()+sequence_edit.lower())
else:
    print(first+sequence_edit)