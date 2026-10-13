FROM python:3.12-slim
RUN apt-get update && apt-get install -y --no-install-recommends git make g++ gcc curl ca-certificates && rm -rf /var/lib/apt/lists/* \
 && git clone -q https://github.com/arminbiere/cadical /c && cd /c && git checkout -q c60730422e758ef1cebe7aeddf2dda31c996bf04 && ./configure >/dev/null && make -j4 >/dev/null && cp build/cadical /usr/local/bin \
 && git clone -q https://github.com/marijnheule/drat-trim /d && cd /d && git checkout -q 2e3b2dc0ecf938addbd779d42877b6ed69d9a985 && gcc -O2 -o /usr/local/bin/lrat-check lrat-check.c \
 && pip install -q chess==1.11.2 \
 && curl -sSf https://raw.githubusercontent.com/leanprover/elan/v4.1.2/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.34.0
ENV PATH=/root/.elan/bin:$PATH
COPY src/chk_strict.cpp src/chk_big.c /b/
RUN g++ -O2 -std=c++17 -o /usr/local/bin/chk_strict /b/chk_strict.cpp && gcc -O2 -o /usr/local/bin/chk_big /b/chk_big.c
ENV B1_CADICAL=/usr/local/bin/cadical B1_CHK1=/usr/local/bin/chk_strict B1_CHK2=/usr/local/bin/chk_big B1_CHK3=/usr/local/bin/lrat-check
WORKDIR /r
COPY . .
CMD ["sh", "-c", "python3 src/cover.py --sample 40 --resolve 6 && python3 src/allcheck/difftest.py edge 20 1 && python3 src/allcheck/cover63.py --sample 20 --resolve 2"]
