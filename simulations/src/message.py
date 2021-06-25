from config import config


class Message:
    def decrement_count(self):
        pass

    def should_forward(self):
        pass

    def __repr__(self):
        pass


class ShareMessage(Message):
    def __init__(self, *, share):
        super().__init__()
        self.share = share
        self.counter = int(config['p2p']['forward_count'])

    def decrement_count(self):
        self.counter -= 1

    def should_forward(self):
        return self.counter > 0

    def __repr__(self):
        return f'share: {self.share} c: {self.counter}'


class NackMessage(Message):
    def __init__(self, *, nack_hash):
        super().__init__()
        # nacks should not be forwarded
        self.counter = -1
        self.nack_hash = nack_hash

    def decrement_count(self):
        pass

    def should_forward(self):
        return False

    def __repr__(self):
        return f'nack: {self.nack_hash}'
