class CheckWord:

    def __init__(self, word):
        self.word = word

    def check_word(self):
        if self.word.upper():
            if self.word[0].lower() and self.word[1:].upper:
                print(self.word.capitalize())
        else:
            print(self.word)


a = CheckWord(input())
a.check_word()