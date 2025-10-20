<#
.SYNOPSIS
  Symbolically links (or deletes) string-code to Mathematica's user applications folder.

.DESCRIPTION
  The default behavior produces the link. Calling the script with the optional -Delete flag will remove
  the link.

.EXAMPLE
  .\windows_symlink.ps1

.EXAMPLE
  .\windows_symlink.ps1 -Delete
#>

param(
    [switch]$Delete
)

$IsAdmin = ([Security.Principal.WindowsPrincipal] [Security.Principal.WindowsIdentity]::GetCurrent()).IsInRole(
    [Security.Principal.WindowsBuiltInRole]::Administrator
)

if (-not $IsAdmin) {
	Write-Host "This script needs administrator priveleges." -ForegroundColor Yellow
	exit 1
}

# Enforce "no other arguments"
if ($args.Count -gt 0) {
	Show-Usage
	exit 1
}
# (PowerShell will normally throw on unknown named parameters before the script runs,
# but checking $args ensures positional extras are caught.)

function Show-Usage {
    <#
    .SYNOPSIS
        Displays help and usage information for this script.
    #>
    Write-Host ""
    Write-Host "Usage:"
    Write-Host "  .\$(Split-Path -Leaf $PSCommandPath) [-Delete]" -ForegroundColor Yellow
    Write-Host ""
}

function Test-SymbolicLink {
    <#
    .DESCRIPTION
        Returns $true if the path exists and is a symbolic link (ReparsePoint),
        otherwise returns $false.

    .PARAMETER Path
        The file or directory path to check.

    .EXAMPLE
        Test-SymbolicLink -Path "C:\Link\MyFileLink.txt"

    .EXAMPLE
        if (Test-SymbolicLink "C:\Link\MyDirLink") {
            Write-Host "It's a symlink!"
        }

    .NOTES
        Works on Windows PowerShell 5+ and PowerShell 7+.
        Reparse points include symbolic links, junctions, and mount points.
    #>

    [CmdletBinding()]
    param(
        [Parameter(Mandatory, Position = 0)]
        [string]$Path
    )

    # Ensure the path exists
    if (-not (Test-Path -LiteralPath $Path)) {
        return $false
    }

    try {
        $item = Get-Item -LiteralPath $Path -Force
        # Check for ReparsePoint attribute
        return ($item.Attributes -band [IO.FileAttributes]::ReparsePoint)
    }
    catch {
        Write-Verbose "Error checking path '$Path': $_"
        return $false
    }
}

$ApplicationsDir = "$home\AppData\Roaming\Wolfram\Applications"
$StringCodeDir = "$PWD\StringCode"
$StringCodeLink = "$ApplicationsDir\StringCode"

# Script main logic
if (-not (Test-Path -Path $StringCodeDir)) {
	Write-Host "Call this script in the git directory containing StringCode." -ForegroundColor Yellow 
	exit 1
}

if (-not (Test-Path -Path $ApplicationsDir)) {
	Write-Host "Mathematica installation not found." -ForegroundColor Red
	exit 1
}

if ($Delete) {
	if (Test-Symboliclink $StringCodeLink) {
		Remove-Item -Path $StringCodeLink -Force -Confirm:$false
	}
	exit 0
}

if (Test-Path $StringCodeLink) {
	Write-Host "StringCode already in applications folder." -ForegroundColor Yellow
	exit 1
}

$LinkCmd = "New-Item -ItemType SymbolicLink -Target `"$StringCodeDir`" -Path `"$StringCodeLink`""

iex $LinkCmd
exit 0
