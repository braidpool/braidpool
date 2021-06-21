
class Share:
    def __init__(self, *, source, heads, env):
        self.timestamp = env.now
        self.source = source
        self.heads = heads

    def __repr__(self):
        return f't: {self.timestamp} s: {self.source} h: {self.heads}'
