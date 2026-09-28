#!/usr/bin/env python3
"""Deterministic local TLC stand-in for the runner's profile/row contract."""

import os
import re
import sys

if "-help" in sys.argv:
    print("TLC2 Version 2.19 of 08 August 2024")
    raise SystemExit(0)


def option(name, fallback):
    if name not in sys.argv:
        return fallback
    return int(sys.argv[sys.argv.index(name) + 1])


# This local fixture models the *observed* OpenJDK 8u504 ParallelGC heap
# readback for the tested -Xmx values; banner heap is not the delivered -Xmx.
# A default-style run intentionally carries no JVM pickup witness.
effective_heaps = {4096: 3641, 9216: 8192, 14336: 12743, 16384: 14564}
fp = option("-fp", 7)
seed = option("-seed", 17)
java_options = os.environ.get("JAVA_TOOL_OPTIONS", "")
heap = re.search(r"(?:^|\s)-Xmx(\d+)m(?:\s|$)", java_options)
if heap:
    if not os.environ.get("FAKE_TLC_SUPPRESS_PICKUP"):
        print(f"Picked up JAVA_TOOL_OPTIONS: {java_options}")
    heap_mib = effective_heaps[int(heap.group(1))]
else:
    heap_mib = 14247
ambient = os.environ.get("_JAVA_OPTIONS")
if ambient:
    print(f"Picked up _JAVA_OPTIONS: {ambient}")
    override = re.search(r"(?:^|\s)-Xmx(\d+)m(?:\s|$)", ambient)
    if override:
        # Measured by the reviewer on the pinned JRE: this later JVM channel
        # overrides JAVA_TOOL_OPTIONS=-Xmx14336m while leaving its pickup intact.
        heap_mib = {1000: 958}[int(override.group(1))]
fp = int(os.environ.get("FAKE_TLC_FORCE_FP", fp))
print("TLC2 Version 2.19 of 08 August 2024")
print(
    f"Running breadth-first search Model-Checking with fp {fp} and seed {seed} "
    f"with 1 worker on 20 cores with {heap_mib}MB heap and 64MB offheap memory "
    "(Linux amd64, OpenJDK 1.8.0_504, MSBDiskFPSet, DiskStateQueue)."
)
print("Starting... (2026-09-27 00:00:00)")
print("Model checking completed. No error has been found.")
print("73 states generated, 36 distinct states found, 0 states left on queue.")
print("The depth of the complete state graph search is 11.")
