from hashlib import sha256

from config import config


class Share:
    def __init__(self, *, source, heads, seq_no, is_block, env):
        self.timestamp = env.now
        self.seq_no = seq_no
        self.source = source
        self.heads = heads
        if config.getboolean('shares', 'simple_hash'):
            self.hash = self.get_simple_hash()
        else:
            self.hash = self.get_hash()
        self.is_block = is_block

    def get_hash(self):
        joined_heads = "".join(self.heads)
        return sha256(f'{self.timestamp}{self.source}{joined_heads}'.
                      encode()).hexdigest()

    def get_simple_hash(self):
        return f'{self.source}-{self.seq_no}'

    def __repr__(self):
        short_heads = [head[0:5] for head in self.heads]
        is_block = 1 if self.is_block else 0
        return (f't: {int(self.timestamp)} s: {self.source} hd: {short_heads} '
                f'b: {is_block} h: {self.hash[0:5]}')
