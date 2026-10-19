FROM python:latest

COPY requirements.txt requirements.txt
RUN pip3 install -r requirements.txt

COPY . .

CMD [ "python3", "simulator_api.py", "--host=0.0.0.0"]