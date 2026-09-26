"""Structured logging helpers for Braidpool functional tests."""

from __future__ import annotations

import json
import logging
import sys
import time
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterator


_MAX_FIELD_LENGTH = 512
_SENSITIVE_KEY_PARTS = (
    "api_key",
    "auth",
    "cookie",
    "passphrase",
    "password",
    "rpcpass",
    "secret",
    "token",
)


class JsonLineFormatter(logging.Formatter):
    """Format log records as one JSON object per line."""

    def format(self, record: logging.LogRecord) -> str:
        payload: dict[str, Any] = {
            "timestamp": datetime.now(tz=timezone.utc).isoformat(timespec="milliseconds"),
            "level": record.levelname,
            "logger": record.name,
            "event": getattr(record, "bp_event", record.getMessage()),
            "message": record.getMessage(),
        }
        fields = getattr(record, "bp_fields", None)
        if fields:
            payload["fields"] = fields
        if record.exc_info:
            payload["traceback"] = self.formatException(record.exc_info)
        return json.dumps(payload, sort_keys=True, default=str)


def configure_file_logger(
    name: str | None,
    log_path: Path,
    *,
    level: str | int = "INFO",
) -> logging.Logger:
    """Create a logger writing structured JSON lines to *log_path*.

    Pass *name=None* to configure the root logger.
    """
    logger = logging.getLogger(name)
    logger.setLevel(level)
    logger.propagate = False

    for handler in list(logger.handlers):
        handler.close()
        logger.removeHandler(handler)

    log_path.parent.mkdir(parents=True, exist_ok=True)
    handler = logging.FileHandler(log_path, encoding="utf8")
    handler.setFormatter(JsonLineFormatter())
    logger.addHandler(handler)
    return logger


def configure_stream_logger(
    name: str | None,
    *,
    level: str | int = "INFO",
) -> logging.Logger:
    """Create a logger writing structured JSON lines to stderr.

    Pass *name=None* to configure the root logger, which catches all
    module-level loggers that have not installed their own handlers.
    """
    logger = logging.getLogger(name)
    logger.setLevel(level)
    logger.propagate = False

    for handler in list(logger.handlers):
        handler.close()
        logger.removeHandler(handler)

    handler = logging.StreamHandler(sys.stderr)
    handler.setFormatter(JsonLineFormatter())
    logger.addHandler(handler)
    return logger


def close_logger(logger: logging.Logger) -> None:
    """Flush, close, and detach all handlers owned by *logger*."""
    for handler in list(logger.handlers):
        handler.flush()
        handler.close()
        logger.removeHandler(handler)


def log_event(
    logger: logging.Logger,
    event: str,
    *,
    level: int = logging.INFO,
    message: str | None = None,
    **fields: Any,
) -> None:
    """Write a structured event without exposing sensitive field values."""
    logger.log(
        level,
        message or event,
        extra={
            "bp_event": event,
            "bp_fields": _sanitize(fields),
        },
    )


def log_exception(
    logger: logging.Logger,
    event: str,
    exc: BaseException,
    **fields: Any,
) -> None:
    """Write an exception event with type, message, and traceback."""
    log_event(
        logger,
        event,
        level=logging.ERROR,
        message=str(exc),
        exception_type=type(exc).__name__,
        exception_message=str(exc),
        **fields,
    )
    logger.error(
        str(exc),
        exc_info=(type(exc), exc, exc.__traceback__),
        extra={
            "bp_event": f"{event}_traceback",
            "bp_fields": _sanitize(fields),
        },
    )


def log_duration(
    logger: logging.Logger,
    event: str,
    duration_seconds: float,
    *,
    status: str = "ok",
    level: int = logging.INFO,
    **fields: Any,
) -> None:
    """Write a duration event using milliseconds."""
    log_event(
        logger,
        event,
        level=level,
        duration_ms=round(duration_seconds * 1000, 3),
        status=status,
        **fields,
    )


def log_rpc_call(
    logger: logging.Logger,
    method: str,
    duration_seconds: float,
    *,
    status: str,
    request_id: int | None = None,
    attempt: int | None = None,
    params: Any = None,
    error: str | None = None,
) -> None:
    """Write a structured RPC timing event with redacted optional parameters."""
    fields: dict[str, Any] = {
        "method": method,
        "duration_ms": round(duration_seconds * 1000, 3),
        "status": status,
    }
    if request_id is not None:
        fields["request_id"] = request_id
    if attempt is not None:
        fields["attempt"] = attempt
    if params is not None:
        fields["params"] = params
    if error is not None:
        fields["error"] = error
    log_event(
        logger,
        "rpc_call",
        level=logging.INFO if status == "ok" else logging.WARNING,
        **fields,
    )


@contextmanager
def log_timed(
    logger: logging.Logger,
    event: str,
    **fields: Any,
) -> Iterator[None]:
    """Measure a code block and log success or exception duration."""
    started = time.monotonic()
    try:
        yield
    except Exception as exc:
        log_duration(logger, event, time.monotonic() - started, status="error", **fields)
        log_exception(logger, f"{event}_failed", exc, **fields)
        raise
    else:
        log_duration(logger, event, time.monotonic() - started, **fields)


def _sanitize(value: Any, key: str = "") -> Any:
    if any(part in key.lower() for part in _SENSITIVE_KEY_PARTS):
        return "<redacted>"
    if isinstance(value, dict):
        return {str(item_key): _sanitize(item_value, str(item_key)) for item_key, item_value in value.items()}
    if isinstance(value, (list, tuple)):
        return [_sanitize(item) for item in value]
    if isinstance(value, str) and len(value) > _MAX_FIELD_LENGTH:
        return value[:_MAX_FIELD_LENGTH] + "...<truncated>"
    return value
