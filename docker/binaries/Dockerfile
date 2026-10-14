FROM scratch
COPY payload/ /
LABEL org.opencontainers.image.source="https://github.com/kjanat/shellcheck-rs"
# A command is required by docker create, but these images are only for copying.
CMD ["/rshellcheck"]
