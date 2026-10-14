FROM scratch
ARG TARGETARCH
COPY ${TARGETARCH}/rshellcheck /bin/rshellcheck
COPY LICENSE.txt /LICENSE.txt
LABEL org.opencontainers.image.source="https://github.com/kjanat/shellcheck-rs" \
      org.opencontainers.image.licenses="GPL-3.0-only"
WORKDIR /w
ENTRYPOINT ["/bin/rshellcheck"]
CMD ["--help"]
