class CheckWord:

    def __init__(self, word):
        self.word = word

    def check_word(self):
        print(self.word.capitalize())

a = CheckWord(input())
a.check_word()