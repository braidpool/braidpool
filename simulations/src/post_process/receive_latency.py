import argparse
import re
from collections import defaultdict

from numpy import mean


class ReceiveLatency:
    def __init__(self):
        self.send_re = r"(\d+) s.*h: (\d+)-(\d+)"
        self.receive_re = r"(\d+) r n: (\d+).*h: (\d+)-(\d+)"
        self.sent_at = defaultdict(int)
        self.latencies = defaultdict(lambda: defaultdict(int))
        self.num_received = defaultdict(int)
        self.num_sent = defaultdict(int)

    def _get_send_details(self, line):
        match = re.match(self.send_re, line)
        if match:
            return match[1], match[2], match[3]
        return None, None, None

    def _get_receive_details(self, line):
        match = re.match(self.receive_re, line)
        if match:
            return match[1], match[2], match[3], match[4]
        return None, None, None, None

    def run(self, logfile):
        with open(logfile, "r") as file:
            for line in file:
                sent_at, sender, msg_seqno = self._get_send_details(line)
                if sent_at:
                    self.num_sent[sender] += 1
                    self.sent_at[f"{sender}-{msg_seqno}"] = int(sent_at)
                else:
                    received_at, receiver, sender, msg_seqno = self._get_receive_details(line)
                    mid = f"{sender}-{msg_seqno}"
                    if received_at and sender != receiver:
                        self.num_received[receiver] += 1
                        if receiver not in self.latencies[mid]:
                            self.latencies[mid][receiver] = int(received_at) - self.sent_at[mid]

    def get_average_latencies(self):
        return {m: mean(list(latencies.values())) for m, latencies in self.latencies.items()}

    def get_average_latency(self):
        return mean(list(self.get_average_latencies().values()))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log_file", "-f", type=str, help="Log file")
    args = parser.parse_args()
    processor = ReceiveLatency()
    processor.run(args.log_file)
    print(processor.get_average_latency())
