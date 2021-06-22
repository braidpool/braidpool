from config import config


class Message:
    def __init__(self, *, share):
        self.share = share
        self.counter = int(config['p2p']['forward_count'])

    def decrement_count(self):
        self.counter -= 1

    def should_forward(self):
        return self.counter > 0

    def __repr__(self):
        return f'{self.share} c: {self.counter}'
