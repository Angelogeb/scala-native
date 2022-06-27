#!/bin/bash

sbt 'set sandbox/nativeMode := "release-fast"; sandbox/nativeLink' && python3.8 benchmarks.py && sbt 'sandbox/clean'
