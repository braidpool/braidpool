import argparse
import re
from collections import defaultdict


class ReceiveLatency:
    def __init__(self):
        self.send_re = r"(\d+) s.*h: (\d+)-(\d+)"
        self.receive_re = r"(\d+) r n: (\d+).*h: (\d+)-(\d+)"
        self.sent_at = defaultdict(int)
        self.latencies = defaultdict(list)
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
                    if received_at:
                        self.num_received[receiver] += 1
                        self.latencies[f"{receiver}-{msg_seqno}"].append(
                            int(received_at) - self.sent_at[f"{sender}-{msg_seqno}"]
                        )

    def print_results(self):
        print(self.latencies)
        #[latencies for m, latencies in self.latencies]


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--log_file", "-f", type=str, help="Log file")
    args = parser.parse_args()
    processor = ReceiveLatency()
    processor.run(args.log_file)
    processor.print_results()
