import InteropHostname

/-- Print the hostname that the native syscall reports. -/
def main : IO Unit := do
  IO.println (← InteropHostname.get)
