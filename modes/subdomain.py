import socket


class EnumerateSubdomain:

    def __init__():
        self.domain     = None
        self.input_file = None

    def find_subdomains(self):

        with open(self.input_file, encoding="utf-8") as file:
            names = [line.strip() for line in file if line.strip()]
        
        for name in names:
            host = name if name.endswith(f".{domain}") else f"{name}.{domain}"

            try:
                addresses = sorted({
                    result[4][0]
                    for result in get.addrinfo(host, None)
                    })
                return f"{host}, {', '.join(addresses)}"

                
            except socket.gaierror:
                return f"{host}: No DNS Result"