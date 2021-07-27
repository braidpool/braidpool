import copy

from config import config


class Message:
    def decrement_count(self):
        pass

    def should_forward(self):
        pass

    def __repr__(self):
        pass

    def copy(self):
        return copy.copy(self)


class ShareMessage(Message):
    forward_count = int(config["p2p"]["forward_count"])

    def __init__(self, *, share):
        super().__init__()
        self.share = share
        self.counter = self.forward_count

    def decrement_count(self):
        self.counter -= 1

    def should_forward(self):
        return self.counter > 0

    def __repr__(self):
        return f"{self.share} c: {self.counter}"

    def copy(self):
        copied = ShareMessage(share=self.share)
        copied.counter = self.counter
        return copied


class NackMessage(Message):
    def __init__(self, *, hash):
        super().__init__()
        # nacks should not be forwarded
        self.counter = -1
        self.hash = hash

    def decrement_count(self):
        pass

    def should_forward(self):
        return False

    def __repr__(self):
        return f"{self.hash}"
