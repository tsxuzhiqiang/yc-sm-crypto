const {BigInteger} = require('jsbn')
const {encodeDer, decodeDer} = require('./asn1')
const _ = require('./utils')
const sm3 = require('./sm3').sm3

const {G, curve, n} = _.generateEcparam()
const C1C2C3 = 0

/**
 * SM2 加密
 * @param msg 要加密的原始字符串
 * @param publicKey 16进制的公钥
 * @param cipherMode 0: C1C2C3模式 1: C1C3C2模式
 */
function encryptHex(msgHex, publicKeyHex, cipherMode = 1) {

    msg =  _.hexToArray(_.utf8ToHex(msg));//将字符串转成16进制
}
