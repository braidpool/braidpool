import { useState } from 'react';

export default function useCopyToClipboard(timeout = 1500) {
  const [copied, setCopied] = useState<string | null>(null);

  const copy = (text: string) => {
    navigator.clipboard.writeText(text).then(() => {
      setCopied(text);
      setTimeout(() => setCopied(null), timeout);
    });
  };

  return { copied, copy };
}
