class Borer < Formula
  desc "Reverse-engineering engine for AI agents: MCP server and CLI"
  homepage "https://github.com/imjustprism/borer"
  version "0.2.5"
  license "AGPL-3.0-only"

  on_macos do
    on_arm do
      url "https://github.com/imjustprism/borer/releases/download/v0.2.5/borer-v0.2.5-aarch64-apple-darwin.tar.gz"
      sha256 "954a74fcf4e6fee4d599092f960cb32e9b64e5fbab09fdce0d34905d7ad839c6"
    end
    on_intel do
      url "https://github.com/imjustprism/borer/releases/download/v0.2.5/borer-v0.2.5-x86_64-apple-darwin.tar.gz"
      sha256 "e0800b991c4e366d34d051110cd8130c262e5965156a1cf3c5953cb8abddfaf1"
    end
  end

  on_linux do
    on_intel do
      url "https://github.com/imjustprism/borer/releases/download/v0.2.5/borer-v0.2.5-x86_64-unknown-linux-gnu.tar.gz"
      sha256 "861f567a53b36b3cd15b8b15ae27b1a0bcc1cb867f8846505ccaede343d45d63"
    end
  end

  def install
    bin.install "borer"
    prefix.install "THIRD-PARTY-LICENSES", "RUST-STD-COPYRIGHT.html"
  end

  test do
    assert_match "borer #{version}", shell_output("#{bin}/borer --version")
  end
end
