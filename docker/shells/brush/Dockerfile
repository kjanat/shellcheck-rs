ARG BASE
FROM ${BASE} AS build
ARG VERSION
RUN cargo install brush-shell --version "${VERSION}" --locked --root /out

FROM ${BASE}
COPY --from=build /out/bin/brush /usr/local/bin/brush
