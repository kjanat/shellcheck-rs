ARG BASE
FROM ${BASE} AS build
ARG KIND SOURCE SHA256 TAG COMMIT VERSION
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates curl build-essential xz-utils libncurses-dev && rm -rf /var/lib/apt/lists/*
COPY fetch.sh /fetch.sh
WORKDIR /src
RUN sh /fetch.sh
RUN ./configure --disable-gdbm --disable-pcre --with-tcsetpgrp && make -j"$(nproc)" && make DESTDIR=/out install.bin install.modules

FROM ${BASE}
RUN apt-get update && apt-get install -y --no-install-recommends libncurses6 && rm -rf /var/lib/apt/lists/*
COPY --from=build /out/usr/local/bin/zsh /usr/local/bin/zsh
COPY --from=build /out/usr/local/lib/zsh /usr/local/lib/zsh
