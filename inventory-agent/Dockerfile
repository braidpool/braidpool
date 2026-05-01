FROM python:3.12-slim AS builder

WORKDIR /app

COPY requirements.txt .
RUN pip install --no-cache-dir --prefix=/install -r requirements.txt


FROM python:3.12-slim

RUN addgroup --system inventory && adduser --system --ingroup inventory inventory

WORKDIR /app

COPY --from=builder /install /usr/local

COPY main.py models.py store.py ./

USER inventory

ENV PORT=8000

EXPOSE 8000


CMD ["uvicorn", "main:app", "--host", "0.0.0.0", "--port", "8000"]
