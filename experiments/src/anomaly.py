from dataclasses import dataclass

@dataclass
class Configuration:
    alpha: int
    beta: int
    gamma: int
    delta: int

def test_anomaly(con: Configuration):
    

    return False

def main():
    '''
    $o_n$ & $o_d$ & $a_n$ & $a_d$ & multiset period & $\lambda_{\text{set}}$ \\
    $98{,}281$ & $139$ & $68$ & $149$ & $153{,}431$ & $1$ \\
    '''
    configuration = Configuration(alpha=68, beta=149, gamma=98281, delta=139)
    test_anomaly(configuration)
                    